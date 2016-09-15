class Answer < ApplicationRecord
    has_one: question
    belongs_to :user_survey_answer 

end
